## Worker report

Item: lem-sfb-central-torus-semisimple-derived-product. Group: Q36. Date: 2026-10-24.

The module Sheaf.AlgebraicGeometry.GroupScheme.CentralTorusDerivedProduct states
AlgebraicGeometry.centralTorus_semisimple_derived_product with one sorry proof.
It introduces no definitions and proves nothing. The informal statement, proof and
proof dependencies are unchanged. Four already landed definition nodes are added to
stmt_deps to register the exact notions used: def-sfb-semisimple-group-scheme,
def-sfb-tori-multiplicative-type, def-sfb-finite-diagonalizable-group-scheme, and
def-sfb-fppf-group-quotient-presentation. No node or declaration is copied or redefined.

I read the item, every original statement dependency's statement and Lean/mathlib
record, the defining signatures and docstrings, and the four additional definition
nodes and their implementations. The withdrawn CompactObject example has no remaining
declarations; the delivered file uses the prescribed module/public-import/expose header.
No repair note exists for this item.

Source reading: Milne, Algebraic Groups (2017), the local PDF, Proposition 12.46 and
Example 12.47, printed pp.245--246; Proposition 19.21, pp.401--402; proof of Proposition
21.60(b) implies (c), p.442. The seven-step proof docstring reproduces the DAG proof,
including the coordinate-algebra refinement valid for infinitesimal kernels. I also
read the current latest blueprint's
blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/
sk-thm-sf-ctf-stability-direct-images.proof.md to check the inherited route. This is
a supporting statement, not a unit's own target.

Clause-by-clause rendering:

- Algebraically closed field F: `{F : Type u} [Field F] [IsAlgClosed F]`.
- F-group schemes: `G R Q : Grp (Over (Spec (.of F)))`. Their group laws and all
  displayed bundled homomorphisms use the recorded `GrpObj`/`IsMonHom` interfaces.
- Smooth G: `[Smooth G.X.hom]`; connected G: `[ConnectedSpace G.X.left]`, which
  includes nonemptiness; affine G: `[IsAffine G.X.left]`.
- Finite type G: `[LocallyOfFiniteType G.X.hom] [QuasiCompact G.X.hom]`, exactly
  the two components of def-weil-finite-type-morphism.
- The closed subgroup R in G: `(i : R ⟶ G)` and
  `[IsClosedSubgroupScheme i.hom.hom]`. This includes the homomorphism condition
  and injectivity on all algebra-valued points as well as closed immersion.
- R is a torus split over F of any finite rank, including zero:
  `hR : ∃ r : ℕ, Nonempty (R ≅ MultiplicativeType.splitTorus F r)`.
  `splitTorus` is the iterated product of the already recorded G_m, with the
  terminal group in rank zero. Isomorphisms are in group schemes, not bare schemes.
- Centrality of R after every scalar extension:
  `∀ (T : Over (Spec (.of F))) (t : T ⟶ R.X) (g : T ⟶ G.X),
  (t ≫ i.hom.hom) * g = g * (t ≫ i.hom.hom)`.
  All test F-schemes are allowed, in particular Spec A for every F-algebra A;
  universal points also show this is equivalent to equality of the two group
  multiplication morphisms, so it adds no hypothesis beyond scalar centrality.
- The semisimple represented fppf quotient is supplied by `(q : G ⟶ Q)`,
  `hquot : IsFppfGroupQuotient i q` and `hQ : IsSemisimpleGroupScheme Q.X`.
  The quotient predicate specifies the actual kernel and coset sheafification
  universal arrow in the actual fppf topology, with its canonical torsor maps.
  These are exactly a presentation of the represented quotient; no additional
  chosen quotient object is silently substituted. Any representing presentation
  may be used. Its local surjectivity and torsor clauses are consequences of the
  quotient hypothesis for this central closed subgroup, not stronger geometric
  assumptions imposed on G.
- D denotes the scheme-theoretic derived subgroup: the conclusion gives a bundled
  group scheme D, its inclusion d, and `IsDerivedGroupScheme d.hom.hom`. This
  predicate says closed subgroup, factorization of the commutator morphism, and
  minimality among all closed subgroup schemes with that factorization.
- D is smooth, connected, affine, finite type and semisimple:
  `IsSemisimpleGroupScheme D.X` includes each of those five geometric conditions
  and the exact absence of nontrivial smooth connected solvable normal closed
  subgroup schemes. The same predicate renders semisimplicity of Q. Solvability
  uses `GroupSchemeDerivedLength`, whose successor is the same scheme-theoretic
  derived-subgroup predicate and whose zero case is the trivial group scheme.
- The map m is multiplication, and is a homomorphism:
  `∃ ... (m : R.X ⊗ D.X ⟶ G.X) (_ : IsMonHom m), ...` and
  `m = (fst R.X D.X ≫ i.hom.hom) * (snd R.X D.X ≫ d.hom.hom)`.
  The tensor here is the cartesian product in schemes over F with the canonical
  product group law. Multiplication of maps is the Hom-group multiplication
  induced by G. The equality fixes m uniquely as the actual map (t,d) ↦ td.
  Its existence is a theorem conclusion, not a choice used to define any data.
- Faithful flatness: `m.left.appTop.hom.FaithfullyFlat` is faithful flatness of
  F[G] → F[R × D]. For affine schemes this is precisely the coordinate-algebra
  condition in the node (extension of scalars exact and detecting zero modules).
- The scheme-theoretic kernel is `GrpObj.ker m`, the pullback over the unit section.
  `IsFinite (GrpObj.ker m).hom` renders finiteness over the field, equivalently
  finite-dimensional coordinate algebra; no smoothness or reducedness is required.
- Multiplicative type: `IsFiniteDiagonalizableGroupScheme (GrpObj.ker m)` is the
  recorded natural group-valued functor identification with D(M), M finite abelian,
  including the group algebra comultiplication e_m ↦ e_m ⊗ e_m. Because F is
  algebraically closed, this is exactly the node's finite multiplicative type.
- Central kernel: for every test F-scheme T and every kernel point a and product
  point x, `(a ≫ GrpObj.kerι m) * x = x * (a ≫ GrpObj.kerι m)`. This is centrality
  in the source R × D, including infinitesimal points.
- Intersection and specified kernel isomorphism:
  `∃ e : pullback i.hom.hom d.hom.hom ≅ GrpObj.ker m` with
  `e.hom ≫ GrpObj.kerι m = lift (pullback.fst i.hom.hom d.hom.hom)
  ((pullback.snd i.hom.hom d.hom.hom)⁻¹)`.
  The pullback is exactly the scheme-theoretic intersection. Its two projections
  describe the same a in G; inverse of the second projection is composition with
  inversion in D, so the displayed map is (a,a^{-1}). This specifies an actual
  scheme isomorphism and its canonical map, not just an abstract isomorphism of
  rational-point groups. Its compatibility with group laws follows from these
  projections and the centrality already stated.
- The explanatory term 'multiplicative isogeny' introduces no separate conclusion
  beyond the faithful-flat, finite-kernel and multiplicative-type conjuncts above.

Dependency declarations used, with modules (all names without a namespace prefix
below are in AlgebraicGeometry except the indicated CategoryTheory names):

- `Field`: Mathlib.Algebra.Field.Defs; `IsAlgClosed`:
  Mathlib.FieldTheory.IsAlgClosed.Basic. AlgebraicClosure is the dependency's
  concrete closure model, but the algebraically closed clause uses its documented
  `IsAlgClosed` notion directly, as the node requests.
- `Scheme`: Mathlib.AlgebraicGeometry.Scheme; `Smooth`:
  Mathlib.AlgebraicGeometry.Morphisms.Smooth; `ConnectedSpace`:
  Mathlib.Topology.Connected.Basic; `LocallyOfFiniteType`:
  Mathlib.AlgebraicGeometry.Morphisms.FiniteType; `QuasiCompact`:
  Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact.
- `CategoryTheory.GrpObj` and `Grp`: Mathlib.CategoryTheory.Monoidal.Grp;
  `CategoryTheory.IsMonHom` and Hom-group operations: the recorded Mathlib
  monoidal group/monoid and cartesian modules, publicly reexported by
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs.
- `IsClosedSubgroupScheme`, `IsSubgroupScheme`, `IsNormalSubgroupScheme`:
  WeilConjectures.AlgebraicGeometry.GroupScheme.Defs. The closed-subgroup
  interface is used directly; no private subgroup predicate is introduced.
- `CategoryTheory.GrpObj.ker`, `kerι` and their canonical group structure:
  WeilConjectures.Mathlib.CategoryTheory.Monoidal.Cartesian.Grp, reexported
  by the recorded group scheme module.
- `IsDerivedGroupScheme`, `IsSemisimpleGroupScheme`, `GroupSchemeDerivedLength`,
  `IsSolvableGroupScheme`: Sheaf.AlgebraicGeometry.GroupScheme.Semisimple.
- `MultiplicativeType.splitTorus`: Sheaf.AlgebraicGeometry.ToriMultiplicativeType,
  built on `StandardGroupSchemes.multiplicative` in
  Sheaf.AlgebraicGeometry.StandardGroupSchemes.
- `IsFiniteDiagonalizableGroupScheme`:
  Sheaf.AlgebraicGeometry.FiniteDiagonalizableGroupScheme.
- `IsFppfGroupQuotient`:
  Sheaf.AlgebraicGeometry.GroupScheme.AffineNormalQuotientGeometry.
- `RingHom.FaithfullyFlat`: Mathlib.RingTheory.RingHom.FaithfullyFlat.
- Available proof dependencies are imported: the affine quotient module above
  (also a statement dependency); SmoothConnectedDerivedSubgroup,
  SemisimplePerfect, and AffineHomRationalPoints in
  Sheaf.AlgebraicGeometry.GroupScheme. The remaining three proof nodes
  lem-sfb-central-torus-faithful-weight-blocks,
  lem-sfb-semisimple-isogeny-source, and
  lem-sfb-split-torus-subgroups-diagonalizable had no Lean record at reading;
  their imports are omitted until they are stated. They are not needed to type
  this statement. Their proof steps remain explicitly documented.

Edge cases checked mathematically before writing and reread against the Lean:

- Rank r = 0 is allowed. Then R is trivial and the conclusion reduces to a
  semisimple G being its own derived group with trivial multiplication kernel.
- Trivial G, R and Q are allowed: the derived series has length zero and
  semisimplicity permits the trivial group. No positive rank or dimension binder.
- G = R a torus and Q trivial gives D trivial and m the torus identity.
- G = GL_n with scalar R = G_m gives D = SL_n and kernel mu_n as in Milne's
  Example 12.47. In characteristic p dividing n this kernel is nonreduced.
  The signature admits it: neither IsFinite nor the finite diagonalizable
  predicate assumes etaleness, smoothness, separability or cardinality of points.
- All scalar F-algebras, including nonreduced ones, appear among the test schemes.
  The inverse diagonal is specified as a scheme morphism, so it detects mu_p.
- An empty scheme cannot be a group scheme over the nonempty Spec F because of
  the unit, and ConnectedSpace G additionally records the stated nonemptiness.
- The explicit universe u is shared by F, schemes and test algebras. No test
  universe is artificially below the scheme universe; the universal-point
  characterization ensures no larger scalar extension is excluded mathematically.

Searches made with the prescribed msearch.py wrapper (Q36, this item):

- LeanFinder: 'A smooth connected affine group with a central torus and semisimple
  quotient is the almost direct product of its central torus and semisimple derived
  subgroup' returned 8 hits (Lie-group products, abstract solvable groups and
  semisimple Lie algebras), no scheme-theoretic theorem.
- LeanSearch: 'A connected algebraic group with central torus and semisimple quotient
  is the product of this torus and its semisimple derived subgroup with finite central
  kernel' returned 8 hits, including Subgroup.center.isMulCommutative,
  Subgroup.finiteIndex_center, Prod.instLieGroup and solvable_prod; no match.
- Loogle: '"GroupScheme", "commutator"' returned 0 hits.
- Mathlib grep: 'centralIsogeny|central_isogeny|ReductiveGroup|SemisimpleGroup|
  almostDirectProduct' returned 0 hits.
- rg over lean/WeilConjectures and lean/Sheaf for centralTorus, central_torus,
  IsSplitTorus, IsMultiplicativeType, IsDiagonalizable, IsSemisimpleGroupScheme and
  IsDerivedGroupScheme found the four reused definitions above and their consumers,
  but no existing theorem with this statement. Read their full implementations.
- grep -rn of the item id in lean/WeilConjectures returned no match. rg of the chosen
  declaration/module names in Mathlib, WeilConjectures, Sheaf and
  dag/lean_names_upstream.json returned no collision.
- Searched definition nodes for torus, diagonalizable, derived subgroup and
  semisimple; reused the already landed definition nodes rather than adding nodes.

No statement dispute or mathematical node fault found. No new nodes and no
replacement dependency modules. The Lean file has explicit autoImplicit false,
no diagnostic commands, no local definitions or notation, and one named theorem
with the complete seven-step proof docstring.

Validation: prescribed scompile.py compiled both the sandbox and the actual module
successfully (2.5 s and 2.8 s), with no errors or warnings. The first draft's bundled
product map exposed a typeclass elaboration mismatch for its kernel; it was replaced
by a map from the underlying cartesian product with an explicit IsMonHom witness.
This changes only the encoding, not the objects or mathematical statement.

## Second reading by Q36

A separate pass by the same dispatcher-started worker reopened the node and final
Lean file. No other agent was started, as the task explicitly prohibits it; the
maintainer's independent reading remains the delivery review. This is not claimed
to be a second person.

I reread every hypothesis and conjunct against the mappings above. The semisimple
predicate was unfolded to verify that smoothness, connectedness, affineness and
both finite-type clauses for D are present. The quotient definition was unfolded
to verify the fppf coset sheafification and actual quotient map. Both centrality
clauses quantify over all test schemes. The finite diagonalizable definition was
unfolded to check a finite abelian character group and naturality, including
nonreduced test schemes. The intersection is a pullback of the inclusions rather
than an intersection of rational points. The final equality specifies the first
projection and inverse of the second, so it has exactly the required sign.

No mathematical mismatch remained. The only correction during checking was the
product-map elaboration encoding described above. No hypothesis was added to make
that compile; being a homomorphism remains a conclusion. No source statement,
proof step or proof dependency was changed. Four existing notion nodes were added
to stmt_deps to keep the signature grounded. The item record's lean.statement is
extracted verbatim from the final theorem signature, preserving line breaks.
